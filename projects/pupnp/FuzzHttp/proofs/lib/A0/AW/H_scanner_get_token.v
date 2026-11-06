(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require H_scanner_get_token.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpRepA AWKit AWAuto.
Import ListNotations.
Open Scope Z_scope.

Definition sgt_entryA : Z := 0x889f4.
Definition SEPTAB_A : Z := 0x219c0.
Definition JTAB_A : Z := 0x21358.
Notation sep20 := P0.H_scanner_get_token.sep20.

Definition sgt_post_A (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S T TY MB A cur len lo : Z) (bs : list byte) (tyw : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r cur' : Z) (tb tl : word) (tyw' : word),
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, q); (S + 8, S + 16); (T, T + 16); (TY, TY + 4)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ asan_env asegs m'
    /\ rw_cells asegs m' S [C8 (wz MB); C8 (wz cur'); C4 (wz 0)]
    /\ rw_cells asegs m' T [C8 tb; C8 tl]
    /\ rw_cells asegs m' TY [C4 tyw']
    /\ ( (exists tlz ty, r = PARSE_OK /\ tb = wz (A + cur) /\ tl = wz tlz /\ tyw' = wz ty
             /\ 1 <= tlz /\ cur' = cur + tlz /\ cur' <= len /\ 0 <= ty <= 5
             /\ ((ty = TT_IDENTIFIER \/ ty = TT_WHITESPACE) -> cur' < len)
             /\ (ty = TT_CRLF -> forall i, cur <= i < cur + tlz -> exists b, nth_error bs (Z.to_nat i) = Some b /\ (bv_unsigned b = 13 \/ bv_unsigned b = 10))
             /\ (ty = TT_CRLF -> tlz <= 2))
       \/ ((r = PARSE_INCOMPLETE \/ r = PARSE_FAILURE) /\ cur' = cur /\ tyw' = tyw) )%Z.

Definition sgt_stmt_A {HC : HasCeiling} : Prop :=
  forall (S T TY MB A cur len cap lo : Z) (bs : list byte) (tw1 tw2 tyw : word)
         (q : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),

  rw_cells asegs m S [C8 (wz MB); C8 (wz cur); C4 (wz 0)] ->
  rw_cells asegs m MB (mbuf_cells A len cap) ->
  bytes_at asegs m A bs -> (Z.of_nat (length bs) >= len)%Z -> (0 <= cur <= len)%Z -> (len <= cap)%Z -> (A + cap + 1 < 2^63)%Z ->
  rw_cells asegs m T [C8 tw1; C8 tw2] ->
  rw_cells asegs m TY [C4 tyw] ->

  asan_env asegs m ->
  shw m S 24 -> shw m MB 32 -> shw m T 16 -> shw m TY 4 -> (0 < len -> shw m A len) -> shw m SEPTAB_A 20 ->

  0x609000 <= S -> S + 24 <= alloc_ceiling -> S mod 8 = 0 ->
  0x609000 <= MB -> MB + 32 <= alloc_ceiling -> MB mod 8 = 0 ->
  0x609000 <= T -> (q <= T \/ T + 16 <= alloc_ceiling) -> T mod 8 = 0 ->
  0x609000 <= TY -> q <= TY -> TY mod 4 = 0 ->
  (0 <= A)%Z -> (A + Z.of_nat (length bs) <= alloc_ceiling)%Z ->

  (MB + 32 <= S)%Z ->
  (T + 16 <= TY \/ TY + 4 <= T)%Z ->
  (T + 16 <= MB \/ S + 24 <= T)%Z ->
  (T + 16 <= A \/ A + Z.of_nat (length bs) <= T)%Z ->
  (A + Z.of_nat (length bs) <= MB \/ S + 24 <= A)%Z ->

  stk asegs m lo q -> alloc_ceiling <= lo -> q < 2^64 -> lo <= q - 128 - A0_RT_STACK ->
  mem_inv asegs m -> a0 = wz S -> a1 = wz T -> a2 = wz TY ->
  evt asegs (sgt_post_A ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S T TY MB A cur len lo bs tyw m)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz sgt_entryA) fc None m (seg_rom asegs)).

Lemma sep_bytes_A : forall m, mem_inv asegs m -> bytes_at asegs m SEPTAB_A sep20.
Proof.
  intros m MI. pose proof (ro_cells_image asegs m SEPTAB_A sep20 MI ltac:(vm_compute; reflexivity) ltac:(unfold SEPTAB_A; lia) ltac:(unfold SEPTAB_A; cbn; lia)) as RO.
  destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Definition jt104_A : list byte := map (Z_to_bv 8)
  [184; 119; 6; 0; 120; 121; 6; 0; 20; 121; 6; 0; 20; 121; 6; 0; 196; 121; 6; 0; 20; 121; 6; 0; 20; 121; 6; 0;
   20; 121; 6; 0; 20; 121; 6; 0; 20; 121; 6; 0; 20; 121; 6; 0; 20; 121; 6; 0; 20; 121; 6; 0; 20; 121; 6; 0;
   20; 121; 6; 0; 20; 121; 6; 0; 20; 121; 6; 0; 20; 121; 6; 0; 20; 121; 6; 0; 20; 121; 6; 0; 20; 121; 6; 0;
   20; 121; 6; 0; 20; 121; 6; 0; 184; 119; 6; 0; 20; 121; 6; 0; 52; 122; 6; 0]%Z.

Definition jt_off_A (c : Z) : Z :=
  if ((c =? 9) || (c =? 32))%Z%bool then 423864 else if (c =? 10)%Z then 424312 else if (c =? 13)%Z then 424388
  else if (c =? 34)%Z then 424500 else 424212.
Lemma jt_bytes_A : forall m, mem_inv asegs m -> bytes_at asegs m JTAB_A jt104_A.
Proof.
  intros m MI. pose proof (ro_cells_image asegs m JTAB_A jt104_A MI ltac:(vm_compute; reflexivity) ltac:(unfold JTAB_A; lia) ltac:(unfold JTAB_A; cbn; lia)) as RO.
  destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.
Lemma jt_entry_A : forall j : nat, (j < 26)%nat ->
  firstn 4 (skipn (4 * j) jt104_A) = le4 (Z_to_bv 64 (jt_off_A (Z.of_nat j + 9))).
Proof.
  intros j Hj. apply P0.H_scanner_get_token.bytes_eqb_eq.
  do 26 (destruct j as [|j]; [vm_compute; reflexivity|]). lia.
Qed.
Lemma jt_read_A : forall m c, mem_inv asegs m -> (9 <= c <= 34)%Z ->
  ov_read_bytes asegs m (wa (JTAB_A + 4 * (c - 9))) 4 = Some (le4 (Z_to_bv 64 (jt_off_A c))).
Proof.
  intros m c MI Hc. pose proof (jt_bytes_A m MI) as B.
  rewrite (bytes_at_read asegs m JTAB_A jt104_A (4 * (c - 9)) 4 B) by (cbn; lia).
  replace (Z.to_nat (4 * (c - 9))) with (4 * Z.to_nat (c - 9))%nat by lia.
  rewrite jt_entry_A by lia. repeat f_equal. lia.
Qed.

Section W.
Context {HC : HasCeiling}.
Hypothesis IC : icpt_contracts.
Variables (S T TY MB A cur len cap lo q : Z) (bs : list byte) (tw1 tw2 tyw : word).
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem).
Hypothesis LBS : Z.of_nat (length bs) >= len.
Hypothesis CUR : 0 <= cur <= len.
Hypothesis CAP : len <= cap.
Hypothesis AHI : A + cap + 1 < 2^63.
Hypothesis AE0 : asan_env asegs m0.
Hypothesis SHWS : shw m0 S 24.
Hypothesis SHWM : shw m0 MB 32.
Hypothesis SHWT : shw m0 T 16.
Hypothesis SHWY : shw m0 TY 4.
Hypothesis SHWA : 0 < len -> shw m0 A len.
Hypothesis SHWP : shw m0 SEPTAB_A 20.
Hypothesis SLO : 0x609000 <= S.
Hypothesis SHI : S + 24 <= alloc_ceiling.
Hypothesis SAL : S mod 8 = 0.
Hypothesis MLO : 0x609000 <= MB.
Hypothesis MHI : MB + 32 <= alloc_ceiling.
Hypothesis MAL : MB mod 8 = 0.
Hypothesis TLO : 0x609000 <= T.
Hypothesis THI : q <= T \/ T + 16 <= alloc_ceiling.
Hypothesis TPAR : T + 16 <= MB \/ S + 24 <= T.
Hypothesis TAA : T + 16 <= A \/ A + Z.of_nat (length bs) <= T.
Hypothesis THI2 : T + 16 <= 2^47.
Hypothesis TAL : T mod 8 = 0.
Hypothesis YLO : 0x609000 <= TY.
Hypothesis YHI : q <= TY.
Hypothesis YHI2 : TY + 4 <= 2^47.
Hypothesis YAL : TY mod 4 = 0.
Hypothesis ALO : 0 <= A.
Hypothesis ABHI : A + Z.of_nat (length bs) <= alloc_ceiling.
Hypothesis MBS : MB + 32 <= S.
Hypothesis TTY : T + 16 <= TY \/ TY + 4 <= T.
Hypothesis APAR : A + Z.of_nat (length bs) <= MB \/ S + 24 <= A.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis QHI : q < 2^64.
Hypothesis LO : lo <= q + -128 - 4096.

Notation W0 := [(lo, q); (S + 8, S + 16); (T, T + 16); (TY, TY + 4)]%Z.
Notation POST := (sgt_post_A ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S T TY MB A cur len lo bs tyw m0).
Notation spw := (Z_to_bv 64 (q + -128)).

Definition minvA (m : mem) (tc1 tc2 : word) : Prop :=
  (exists j24, rw_cells asegs m (q + -128) [CB 24 j24; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
  /\ stk asegs m lo (q + -128)
  /\ rw_cells asegs m S [C8 (wz MB); C8 (wz cur); C4 (wz 0)]
  /\ rw_cells asegs m MB [C8 (wz A); C8 (wz len); C8 (wz cap); C8 (wz 5)]
  /\ bytes_at asegs m A bs
  /\ rw_cells asegs m T [C8 tc1; C8 tc2]
  /\ rw_cells asegs m TY [C4 tyw]
  /\ mem_inv asegs m
  /\ munch W0 m0 m /\ wmono asegs m0 m.

#[using="HC AE0 SLO MLO TLO YLO CLO LO"] Lemma ret_errA : forall (r : Z) x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 tc1 tc2 m,
  minvA m tc1 tc2 -> (r = PARSE_INCOMPLETE \/ r = PARSE_FAILURE) ->
  evt asegs POST (MS (mkR x1 spw gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                      F (Z_to_bv 64 0x88eb0) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ([j24 FR] & ST & SC & MBC & BUF & TC & TYC & MI & MU & WM) HR.
  pose proof alloc_ceiling_range as ACR; unfold alloc_floor, alloc_ceiling_max in ACR.
  do 13 step. step.
  env_now AE0 MU WM. release_to q. step.
  unfold sgt_post_A. finish.
  1: exact SC. 1: exact TC. 1: exact TYC. right. split; [exact HR| split; reflexivity].
Qed.

#[using="HC MB bs m0 SHWS SHWT SHWY CLO"] Lemma W0_app : app_ivs W0.
Proof.
  unfold app_ivs. apply Forall_cons; [apply app_iv_stack; exact CLO|].
  apply Forall_cons; [eapply app_iv_of_win_ok; [exact (shw_win_ok _ _ _ SHWS)| lia| lia]|].
  apply Forall_cons; [eapply app_iv_of_win_ok; [exact (shw_win_ok _ _ _ SHWT)| lia| lia]|].
  apply Forall_cons; [eapply app_iv_of_win_ok; [exact (shw_win_ok _ _ _ SHWY)| lia| lia]|].
  apply Forall_nil.
Qed.
#[using="HC MB bs SHWS SHWT SHWY CLO"] Lemma acc_now : forall m X n, shw m0 X n -> munch W0 m0 m -> accessible m X n.
Proof. intros m X n H MU. eapply accessible_frame; [exact (proj1 H)| exact (shw_win_ok _ _ _ H)| exact MU| exact W0_app]. Qed.
#[using="HC MB bs SHWS SHWT SHWY CLO"] Lemma shw_now0 : forall m X n, shw m0 X n -> munch W0 m0 m -> shw m X n.
Proof. intros m X n H MU. exact (shw_frame W0 m0 m X n H MU W0_app). Qed.

#[using="HC S T TY MB A lo q bs SHI THI TPAR TAA YHI ABHI MBS APAR CLO LO"] Lemma acc_loadw : forall (m : mem) APP w (a : word), 1 <= w -> APP mod 8 + w <= 8 -> 0 <= APP ->
  acc m (APP + w - 1) -> a = wa (sh APP) ->
  exists k, ov_read_bytes asegs m a 1 = Some [Z_to_bv 8 k] /\ (k = 0 \/ (0 < k < 8 /\ APP mod 8 + w - 1 < k)).
Proof.
  intros m APP w a W1 W8 AP HACC ->.
  assert (E : sh (APP + w - 1) = sh APP) by (unfold sh; f_equal; Z.div_mod_to_equations; lia).
  assert (E2 : (APP + w - 1) mod 8 = APP mod 8 + w - 1) by (Z.div_mod_to_equations; lia).
  destruct (acc_load m (APP + w - 1) (wa (sh APP)) HACC ltac:(rewrite E; reflexivity)) as (k & R & Hk).
  exists k. split; [exact R|]. rewrite E2 in Hk. exact Hk.
Qed.
Ltac chk8 r APP HS :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of HS with shw _ ?X ?n =>
      match goal with MU : munch _ _ mm |- _ =>
        let HA' := fresh "ACCn" in
        pose proof (acc_now mm X n HS MU) as HA'; acc_chk0 r APP HA'; clear HA' end end end;
  step; clear_shr.

Definition selw (i j k : nat) (yi yj v : word) : word := if Nat.eqb k i then yi else if Nat.eqb k j then yj else v.

Ltac gen2 CONT pcnew i j :=
  let v1 := reg_val 1 in let v2 := reg_val 2 in let v3 := reg_val 3 in let v4 := reg_val 4 in let v5 := reg_val 5 in let v6 := reg_val 6 in let v7 := reg_val 7 in let v8 := reg_val 8 in let v9 := reg_val 9 in let v10 := reg_val 10 in let v11 := reg_val 11 in let v12 := reg_val 12 in let v13 := reg_val 13 in let v14 := reg_val 14 in let v15 := reg_val 15 in let v16 := reg_val 16 in let v17 := reg_val 17 in let v18 := reg_val 18 in let v19 := reg_val 19 in let v20 := reg_val 20 in let v21 := reg_val 21 in let v22 := reg_val 22 in let v23 := reg_val 23 in let v24 := reg_val 24 in let v25 := reg_val 25 in let v26 := reg_val 26 in let v27 := reg_val 27 in let v28 := reg_val 28 in let v29 := reg_val 29 in let v30 := reg_val 30 in let v31 := reg_val 31 in
  lazymatch goal with |- evt ?sg ?P (MS _ ?F _ ?fc ?o ?mm ?ro) =>
    let T := constr:(forall yi yj : word, evt sg P (MS (mkR (selw i j 1%nat yi yj v1) (selw i j 2%nat yi yj v2) (selw i j 3%nat yi yj v3) (selw i j 4%nat yi yj v4) (selw i j 5%nat yi yj v5) (selw i j 6%nat yi yj v6) (selw i j 7%nat yi yj v7) (selw i j 8%nat yi yj v8) (selw i j 9%nat yi yj v9) (selw i j 10%nat yi yj v10) (selw i j 11%nat yi yj v11) (selw i j 12%nat yi yj v12) (selw i j 13%nat yi yj v13) (selw i j 14%nat yi yj v14) (selw i j 15%nat yi yj v15) (selw i j 16%nat yi yj v16) (selw i j 17%nat yi yj v17) (selw i j 18%nat yi yj v18) (selw i j 19%nat yi yj v19) (selw i j 20%nat yi yj v20) (selw i j 21%nat yi yj v21) (selw i j 22%nat yi yj v22) (selw i j 23%nat yi yj v23) (selw i j 24%nat yi yj v24) (selw i j 25%nat yi yj v25) (selw i j 26%nat yi yj v26) (selw i j 27%nat yi yj v27) (selw i j 28%nat yi yj v28) (selw i j 29%nat yi yj v29) (selw i j 30%nat yi yj v30) (selw i j 31%nat yi yj v31)) F (Z_to_bv 64 pcnew) fc o mm ro)) in
    let T' := eval cbv beta iota delta [selw Nat.eqb] in T in
    assert (CONT : T') end.

Ltac chkw r APP w HS k SHR Hk :=
  let a := reg_val r in
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of HS with shw _ ?X ?n =>
      match goal with MU : munch _ _ mm |- _ =>
        destruct (acc_loadw mm APP w a ltac:(lia) ltac:(lia) ltac:(lia) (acc_now mm X n HS MU (APP + w - 1) ltac:(lia)) ltac:(shadow_addr_tac)) as (k & SHR & Hk) end end end.

#[using="HC AE0 SHWS SHWT SHWY SLO SHI MLO TLO THI TPAR TAA YLO YHI YHI2 YAL ABHI MBS TTY APAR CLO LO"] Lemma tailA : forall (tlz ty : Z) x1 x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x19 x20 x21 x25 x26 x27 x28 x29 x30 x31 m,
  minvA m (wz (A + cur)) (wz tlz) ->
  1 <= tlz -> cur + tlz <= len -> 0 <= ty <= 5 ->
  ((ty = 0 \/ ty = 1) -> cur + tlz < len) ->
  (ty = 2 -> forall i, cur <= i < cur + tlz -> exists b, nth_error bs (Z.to_nat i) = Some b /\ (bv_unsigned b = 13 \/ bv_unsigned b = 10)) ->
  (ty = 2 -> tlz <= 2) ->
  evt asegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 TY) x9 (Z_to_bv 64 (T + 8)) (Z_to_bv 64 ty) x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 (S + 8)) x19 x20 x21 (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr (S + 8) 3 + 2147450880))
                          (Z_to_bv 64 cur) x25 x26 x27 x28 x29 x30 x31)
                      F (Z_to_bv 64 0x88e84) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ([j24 FR] & ST & SC & MBC & BUF & TC & TYC & MI & MU & WM) TL1 TL2 TYR STRICT CRB CRL.
  pose proof alloc_ceiling_range as ACR; unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
  chk8 23 (S + 8) SHWS.
  walk_lia_to 0x88ea0.
  gen2 CONT 0x88ea8 10%nat 12%nat.
  { intros y10 y12.
    walk_lia_to 0x88ee4.
    step. env_now AE0 MU WM. release_to q. step.
    unfold sgt_post_A. finish.
    1: exact SC.
    1: exact TC.
    1: exact TYC.
    left. exists tlz, ty. repeat (split; [first [reflexivity| lia]|]).
    split. { intros Hty; unfold TT_IDENTIFIER, TT_WHITESPACE in Hty; specialize (STRICT Hty); lia. }
    unfold TT_CRLF. split; [exact CRB| exact CRL]. }
  chkw 12 TY 4 SHWY k SHR Hk.
  destruct Hk as [-> | [K1 K2]].
  - step. step. lit_branch. apply CONT.
  - step. step. rewrite (sxb_small k) by lia. if_cases K3; zify_cond K3; [| exfalso; lia].
    zstep. zstep. zstep. if_cases K4; zify_cond K4; zify_granule K4; [| exfalso; lia].
    apply CONT.
Qed.
Notation LSTA pc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x25 x26 x27 x28 x29 x30 x31 mm :=
  (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 TY) (Z_to_bv 64 T) x10 x11 x12 x13 x14 x15 x16 x17
           (Z_to_bv 64 (S + 8)) x19 (Z_to_bv 64 S) x21 (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr (S + 8) 3 + 2147450880))
           (Z_to_bv 64 cur) x25 x26 x27 x28 x29 x30 x31)
      F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

#[using="HC LBS CUR AE0 SHWS SHWT SHWY SLO SHI MLO TLO THI TPAR TAA THI2 YLO YHI YHI2 YAL ABHI MBS TTY APAR CLO LO"] Lemma ws_endA : forall (i : Z) x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x26 x27 x28 x29 x30 x31 tc2 m,
  minvA m (wz (A + cur)) tc2 -> cur < i <= len ->
  evt asegs POST (LSTA 0x88e2c x1 x5 x6 x7 x10 (Z_to_bv 64 (A + i)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (A + cur)) x21
                       (Z_to_bv 64 (A + len)) x26 x27 x28 x29 x30 x31 m).
Proof.
  intros until m. intros MV HI. pose proof MV as ([j24 FR] & ST & SC & MBC & BUF & TC & TYC & MI & MU & WM).
  pose proof alloc_ceiling_range as ACR; unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
  walk_lia_to 0x88e38.
  chk8 12 (S + 16) SHWS.
  walk_lia_to 0x88e4c.
  step. if_cases K1; zify_cond K1.
  -   apply (ret_errA 1) with (tc1 := wz (A + cur)) (tc2 := tc2); [exact MV| left; reflexivity].
  - walk_lia_to 0x88e5c.
    chk8 12 (T + 8) SHWT.
    walk_lia_to 0x88e7c.
    chk8 12 (T + 8) SHWT.
    walk_lia_to 0x88e84.
    replace (A + i - (A + cur))%Z with (i - cur)%Z in * by lia.
    apply (tailA (i - cur) 1); try lia.
    split; [eexists; exact FR|]. repeat (split; [assumption|]). assumption.
Qed.
#[using="S T TY MB bs"] Lemma byte_rangeA : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. cbn. lia. Qed.
#[using="S T TY MB LBS SLO MLO TLO YLO"] Lemma nth_bsA : forall i, 0 <= i < len -> exists b, nth_error bs (Z.to_nat i) = Some b.
Proof.
  intros i Hi. destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E; [eexists; reflexivity|].
  apply nth_error_None in E. lia.
Qed.

#[using="HC LBS CUR AE0 SHWS SHWT SHWY SHWA SLO SHI MLO TLO THI TPAR TAA THI2 YLO YHI YHI2 YAL ABHI MBS TTY APAR CLO LO"] Lemma ws_loopA : forall (k : nat) (i : Z) x1 x5 x6 x7 x14 x15 x16 x17 x21 x27 x28 x29 x30 x31 tc2 m,
  len - i < Z.of_nat k -> cur < i < len -> minvA m (wz (A + cur)) tc2 ->
  evt asegs POST (LSTA 0x88b54 x1 x5 x6 x7 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (A + i)) (Z_to_bv 64 32) (Z_to_bv 64 9) x14 x15 x16 x17
                       (Z_to_bv 64 (A + cur)) x21 (Z_to_bv 64 (A + len)) (Z_to_bv 64 (len - i)) x27 x28 x29 x30 x31 m).
Proof.
  induction k as [|k IH]; intros until m; intros HK HI MV; [lia|].
  pose proof MV as ([j24 FR] & ST & SC & MBC & BUF & TC & TYC & MI & MU & WM).
  pose proof alloc_ceiling_range as ACR; unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
  destruct (nth_bsA i ltac:(lia)) as [b Hb]. pose proof (byte_rangeA b) as BR.
  pose proof (u8ro_read asegs m A bs i b (Z_to_bv 64 (A + i)) BUF Hb ltac:(lia) eq_refl) as RD.
  pose proof (SHWA ltac:(lia)) as SHWA'.
  walk_lia_to 0x88b5c.
  gen2 CONT 0x88b64 14%nat 15%nat.
  { intros y14 y15.
    step.
    step. if_cases K1; zify_cond K1.
    -   zstep. zstep. zstep. step. if_cases K2; zify_cond K2.
      +   zstep. apply (ws_endA len) with (tc2 := tc2); [exact MV| lia].
      + replace (len - i + -1)%Z with (len - (i + 1))%Z by lia. replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
        apply (IH (i + 1)%Z) with (tc2 := tc2); [lia| lia| exact MV].
    - step. if_cases K3; zify_cond K3.
      +   zstep. zstep. zstep. step. if_cases K2; zify_cond K2.
        * zstep. apply (ws_endA len) with (tc2 := tc2); [exact MV| lia].
        * replace (len - i + -1)%Z with (len - (i + 1))%Z by lia. replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
          apply (IH (i + 1)%Z) with (tc2 := tc2); [lia| lia| exact MV].
      +   step. apply (ws_endA i) with (tc2 := tc2); [exact MV| lia]. }
  chkw 14 (A + i) 1 SHWA' kk SHR Hk.
  destruct Hk as [-> | [G1 G2]].
  - step. step. lit_branch. apply CONT.
  - step. step. rewrite (sxb_small kk) by lia. if_cases G3; zify_cond G3; [| exfalso; lia].
    zstep. step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
    apply CONT.
Qed.

Definition minvI (m : mem) (tc1 tc2 : word) : Prop :=
  (exists j8, rw_cells asegs m (q + -128) [CB 8 j8; C8 (Z_to_bv 64 (Z.shiftr (S + 8) 3 + 2147450880)); C8 (Z_to_bv 64 TY);
                                          C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
  /\ stk asegs m lo (q + -128)
  /\ rw_cells asegs m S [C8 (wz MB); C8 (wz cur); C4 (wz 0)]
  /\ rw_cells asegs m MB [C8 (wz A); C8 (wz len); C8 (wz cap); C8 (wz 5)]
  /\ bytes_at asegs m A bs
  /\ rw_cells asegs m T [C8 tc1; C8 tc2]
  /\ rw_cells asegs m TY [C4 tyw]
  /\ mem_inv asegs m
  /\ munch W0 m0 m /\ wmono asegs m0 m.

#[using="Type"] Lemma minvI_A : forall m tc1 tc2, minvI m tc1 tc2 -> minvA m tc1 tc2.
Proof.
  intros m tc1 tc2 ([j8 FR] & REST). split; [| exact REST].
  pose proof (rw_cells_merge asegs m (q + -128) [] [CB 8 j8; C8 (Z_to_bv 64 (Z.shiftr (S + 8) 3 + 2147450880)); C8 (Z_to_bv 64 TY)]
                [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] FR) as M.
  cbn [app cells_size csize Nat.add] in M. eexists. exact M.
Qed.

#[using="HC LBS CUR AE0 SHWS SHWT SHWY SLO SHI MLO TLO THI TPAR TAA THI2 YLO YHI YHI2 YAL ABHI MBS TTY APAR CLO LO"] Lemma ident_endA : forall (n : Z) x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x25 x28 x29 x30 x31 tc2 m,
  minvI m (wz (A + cur)) tc2 -> 1 <= n <= len - cur ->
  evt asegs POST (MS (mkR x1 spw gp tp x5 x6 x7 x8 (Z_to_bv 64 T) x10 x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 (S + 8)) x19 (Z_to_bv 64 S) x21 (Z_to_bv 64 2147450880) x23
                          (Z_to_bv 64 cur) x25 (Z_to_bv 64 len) (Z_to_bv 64 (- n)) x28 x29 x30 x31)
                      F (Z_to_bv 64 0x88c08) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MV HN. pose proof MV as ([j8 FR] & ST & SC & MBC & BUF & TC & TYC & MI & MU & WM).
  pose proof alloc_ceiling_range as ACR; unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
  walk_lia_to 0x88c14.
  chk8 11 (S + 16) SHWS.
  walk_lia_to 0x88c34.
  step. if_cases K1; zify_cond K1.
  -   apply (ret_errA 1) with (tc1 := wz (A + cur)) (tc2 := tc2); [exact (minvI_A _ _ _ MV)| left; reflexivity].
  - assert (NE : n <> len - cur). { intros E. apply K1. subst n. f_equal. lia. }
    walk_lia_to 0x88c44.
    chk8 11 (T + 8) SHWT.
    walk_lia_to 0x88c60.
    chk8 12 (T + 8) SHWT.
    walk_lia_to 0x88e84.
    change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0).
    replace (Z_to_bv 64 (0 - - n mod 18446744073709551616)) with (Z_to_bv 64 n) in TC.
    2:{ apply Z_to_bv_eqm. change 18446744073709551616%Z with (2^64)%Z.
        rewrite <- (Z.mod_add (-n) 1 (2^64)) by lia. rewrite (Z.mod_small (-n + 1 * 2^64)) by lia.
        symmetry. rewrite <- (Z.mod_add _ 1 (2^64)) by lia. f_equal. lia. }
    apply (tailA n 0); try lia.
    apply minvI_A. split; [eexists; exact FR|]. repeat (split; [assumption|]). assumption.
Qed.

#[using="S T TY MB bs SLO MLO TLO YLO"] Lemma sep_prefix_le : forall c, 0 <= (let r := memchr_res SEPTAB_A c 20 sep20 in if r =? 0 then 20 else r - SEPTAB_A + 1) <= 20.
Proof.
  intros c. unfold memchr_res. destruct (find_byte c (firstn (Z.to_nat 20) sep20)) as [i|] eqn:E; [| cbn; lia].
  destruct (find_byte_Some _ _ _ E) as (L & _ & _). rewrite firstn_length in L. cbn [length P0.H_scanner_get_token.sep20 map] in L.
  cbv zeta. destruct (Z.eqb_spec (SEPTAB_A + Z.of_nat i) 0); unfold SEPTAB_A in *; lia.
Qed.

Ltac call_memchr cval :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ _ mm |- _ =>
      let SP := fresh "SHWPn" in
      pose proof (shw_now0 mm SEPTAB_A 20 SHWP MU) as SP;
      eapply evt_cut;
      [ eapply (ic_memchr IC) with (A := SEPTAB_A) (c := cval) (n := 20) (buf := sep20) (lo := lo);
        [ apply sep_bytes_A; assumption
        | apply P0.H_scanner_get_token.memchr_ok_sep
        | eapply accessible_sub; [exact (proj1 SP) | lia | pose proof (sep_prefix_le cval); lia]
        | eapply sh_readable_sub; [exact (proj1 (proj2 SP)) | lia | pose proof (sep_prefix_le cval); lia | pose proof (sep_prefix_le cval); lia]
        | apply icpt_rng_intro;
          [ apply (win_ok_sub SEPTAB_A 20 _ _ (proj2 (proj2 SP))); pose proof (sep_prefix_le cval); lia
          | pose proof (sep_prefix_le cval); pose proof alloc_ceiling_range as ACRx; unfold alloc_floor, alloc_ceiling_max in ACRx; unfold SEPTAB_A in *; lia
          | pose proof (sep_prefix_le cval); lia ]
        | assumption | assumption | lia | unfold A0_RT_STACK; lia | lia
        | left; cbn [length P0.H_scanner_get_token.sep20 map]; unfold SEPTAB_A; lia
        | assumption | reflexivity | reflexivity | reflexivity | lia | lia ]
      | clear SP; post_call asegs mm ] end end.

#[using="HC IC LBS CUR AE0 SHWS SHWT SHWY SHWA SHWP SLO SHI MLO TLO THI TPAR TAA THI2 YLO YHI YHI2 YAL ABHI MBS TTY APAR CLO QHI LO"] Lemma ident_loopA : forall (k : nat) (n : Z) x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 tc2 m,
  len - cur - n < Z.of_nat k -> 1 <= n <= len - cur -> minvI m (wz (A + cur)) tc2 ->
  evt asegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 (A + cur + n)) (Z_to_bv 64 T) x10 (Z_to_bv 64 (- n)) x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 (S + 8)) (Z_to_bv 64 SEPTAB_A) (Z_to_bv 64 S) (Z_to_bv 64 (A + cur + n)) (Z_to_bv 64 2147450880)
                          (Z_to_bv 64 94) (Z_to_bv 64 cur) (Z_to_bv 64 (A + len)) (Z_to_bv 64 len) x27 x28 x29 x30 x31)
                      F (Z_to_bv 64 0x88bb4) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros until m; intros HK HN MV; [lia|].
  pose proof MV as ([j8 FR] & ST & SC & MBC & BUF & TC & TYC & MI & MU & WM).
  pose proof alloc_ceiling_range as ACR; unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
  zstep. step. if_cases K1; zify_cond K1.
  -   apply (ident_endA n) with (tc2 := tc2); [exact MV| lia].
  - destruct (nth_bsA (cur + n) ltac:(lia)) as [b Hb]. pose proof (byte_rangeA b) as BR.
    pose proof (u8ro_read asegs m A bs (cur + n) b (Z_to_bv 64 (A + cur + n)) BUF Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    pose proof (SHWA ltac:(lia)) as SHWA'.
    walk_lia_to 0x88bc4.
    gen2 CONT 0x88bcc 10%nat 11%nat.
    { intros y10 y11.
      step. zstep. step. if_cases K2; zify_cond K2.
      +   apply (ident_endA n) with (tc2 := tc2); [exact MV| lia].
      + zstep. zstep. step.
        env_now AE0 MU WM.
        call_memchr (bv_unsigned b).
        clear MV RD AE PC0 POST. rename MI0 into MI. rename PC into ST.
        assert (MV : minvI x24 (wz (A + cur)) tc2).
        { split; [eexists; exact FR|]. repeat (split; [assumption|]). assumption. }
        pose proof (P0.H_scanner_get_token.memchr_res_small SEPTAB_A (bv_unsigned b) 20 sep20 ltac:(unfold SEPTAB_A; lia)) as MR.
        cbn [length P0.H_scanner_get_token.sep20 map] in MR. unfold SEPTAB_A in MR.
        zstep. zstep. zstep. step. if_cases K3; zify_cond K3.
        *
          replace (A + cur + n + 1)%Z with (A + cur + (n + 1))%Z by lia.
          replace (- n + -1)%Z with (- (n + 1))%Z by lia.
          apply (IH (n + 1)%Z) with (tc2 := tc2); [lia| lia| exact MV].
        * step. apply (ident_endA n) with (tc2 := tc2); [exact MV| lia]. }
    chkw 10 (A + cur + n) 1 SHWA' kk SHR Hk.
    destruct Hk as [-> | [G1 G2]].
    + step. step. lit_branch. apply CONT.
    + step. step. rewrite (sxb_small kk) by lia. if_cases G3; zify_cond G3; [| exfalso; lia].
      zstep. step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
      apply CONT.
Qed.

Ltac mv_tacA FR := split; [eexists; exact FR|]; repeat (split; [assumption|]); assumption.

#[using="HC LBS CUR AE0 SHWS SHWT SHWY SLO SHI MLO TLO THI TPAR TAA THI2 TAL YLO YHI YHI2 YAL ABHI MBS TTY APAR CLO LO"] Lemma ctl_blkA : forall x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x25 x26 x27 x28 x29 x30 x31 m,
  minvA m tw1 tw2 -> cur < len ->
  evt asegs POST (LSTA 0x88f18 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (A + cur)) x21 x25 x26 x27 x28 x29 x30 x31 m).
Proof.
  intros until m. intros MV HCL. pose proof MV as ([j24 FR] & ST & SC & MBC & BUF & TC & TYC & MI & MU & WM).
  pose proof alloc_ceiling_range as ACR; unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
  walk_lia_to 0x88f20. chk8 10 T SHWT.
  walk_lia_to 0x88f38. chk8 11 (T + 8) SHWT.
  walk_lia_to 0x88f58. chk8 12 (T + 8) SHWT.
  walk_lia_to 0x88e84.
  apply (tailA 1 3); try lia. mv_tacA FR.
Qed.

#[using="HC IC LBS CUR AE0 SHWS SHWT SHWY SHWP SLO SHI MLO TLO THI TPAR TAA THI2 TAL YLO YHI YHI2 YAL ABHI MBS TTY APAR CLO QHI LO"] Lemma default_blkA : forall (c : Z) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x26 x27 x28 x29 x30 x31 m,
  minvA m tw1 tw2 -> cur < len -> 0 <= c < 256 ->
  evt asegs POST (LSTA 0x88c6c x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (A + cur)) (Z_to_bv 64 c) x25 x26 x27 x28 x29 x30 x31 m).
Proof.
  intros until m. intros MV HCL Hc. pose proof MV as ([j24 FR] & ST & SC & MBC & BUF & TC & TYC & MI & MU & WM).
  pose proof alloc_ceiling_range as ACR; unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
  walk_lia_to 0x88c7c. step.
  env_now AE0 MU WM.
  call_memchr c.
  clear MV AE PC0 POST. rename MI0 into MI. rename PC into ST.
  pose proof (P0.H_scanner_get_token.memchr_res_small SEPTAB_A c 20 sep20 ltac:(unfold SEPTAB_A; lia)) as MR.
  cbn [length P0.H_scanner_get_token.sep20 map] in MR. unfold SEPTAB_A in MR.
  step. if_cases K1; zify_cond K1.
  -   zstep. step. if_cases K2; zify_cond K2.
    +   apply ctl_blkA; [mv_tacA FR| lia].
    + zstep. step. if_cases K3; zify_cond K3.
      *   apply ctl_blkA; [mv_tacA FR| lia].
      *   zstep. step. apply (ret_errA 3) with (tc1 := tw1) (tc2 := tw2); [mv_tacA FR| right; reflexivity].
  -
    walk_lia_to 0x88c8c. chk8 10 T SHWT.
    walk_lia_to 0x88ca4. chk8 11 (T + 8) SHWT.
    walk_lia_to 0x88cc4. chk8 12 (T + 8) SHWT.
    walk_lia_to 0x88e84.
    apply (tailA 1 4); try lia. mv_tacA FR.
Qed.

#[using="HC IC LBS CUR AE0 SHWS SHWT SHWY SHWA SHWP SLO SHI MLO TLO THI TPAR TAA THI2 TAL YLO YHI YHI2 YAL ABHI MBS TTY APAR CLO QHI LO"] Lemma ident_startA : forall x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x27 x28 x29 x30 x31 m,
  minvA m tw1 tw2 -> cur < len ->
  evt asegs POST (LSTA 0x88b80 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (A + cur)) x21 (Z_to_bv 64 (A + len)) (Z_to_bv 64 len)
                       x27 x28 x29 x30 x31 m).
Proof.
  intros until m. intros ([j24 FR] & ST & SC & MBC & BUF & TC & TYC & MI & MU & WM) HCL.
  pose proof alloc_ceiling_range as ACR; unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
  walk_lia_to 0x88b90.
  chk8 10 T SHWT.
  walk_lia_to 0x88bb4.
  apply (ident_loopA (Datatypes.S (Z.to_nat (len - cur))) 1) with (tc2 := tw2); [lia| lia|].
  split; [eexists; exact FR|]. repeat (split; [assumption|]). assumption.
Qed.

#[using="HC LBS CUR AE0 SHWS SHWT SHWY SHWA SLO SHI MLO TLO THI TPAR TAA THI2 YLO YHI YHI2 YAL ABHI MBS TTY APAR CLO LO"] Lemma quote_loopA : forall (k : nat) (i : Z) x1 x5 x6 x7 x17 x21 x26 x27 x28 x29 x30 x31 tc2 m,
  len - i < Z.of_nat k -> cur < i < len -> minvA m (wz (A + cur)) tc2 ->
  evt asegs POST (LSTA 0x88dd0 x1 x5 x6 x7 (Z_to_bv 64 (A + i)) (Z_to_bv 64 92) (Z_to_bv 64 34) (Z_to_bv 64 32) (Z_to_bv 64 13)
                       (Z_to_bv 64 9728) (Z_to_bv 64 127) x17 (Z_to_bv 64 (A + cur)) x21 (Z_to_bv 64 (A + len)) x26 x27 x28 x29 x30 x31 m).
Proof.
  induction k as [|k IH]; intros until m; intros HK HI MV; [lia|].
  pose proof MV as ([j24 FR] & ST & SC & MBC & BUF & TC & TYC & MI & MU & WM).
  pose proof alloc_ceiling_range as ACR; unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
  destruct (nth_bsA i ltac:(lia)) as [b Hb]. pose proof (byte_rangeA b) as BR.
  pose proof (u8ro_read asegs m A bs i b (Z_to_bv 64 (A + i)) BUF Hb ltac:(lia) eq_refl) as RD.
  pose proof (SHWA ltac:(lia)) as SHWA'.

  assert (CONT : forall (i' : Z) y1 y5 y6 y7 y10 y21 y26 y27 y28 y29 y30 y31,
    i < i' <= len ->
    evt asegs POST (LSTA 0x88dc8 y1 y5 y6 y7 y10 (Z_to_bv 64 92) (Z_to_bv 64 34) (Z_to_bv 64 32) (Z_to_bv 64 13)
                         (Z_to_bv 64 9728) (Z_to_bv 64 127) (Z_to_bv 64 (A + i')) (Z_to_bv 64 (A + cur)) y21 (Z_to_bv 64 (A + len)) y26 y27 y28 y29 y30 y31 m)).
  { intros until y31. intros HI'. zstep. step. if_cases KC; zify_cond KC.
    - zstep. step. apply (ret_errA 1) with (tc1 := wz (A + cur)) (tc2 := tc2); [exact MV| left; reflexivity].
    - apply (IH i') with (tc2 := tc2); [lia| lia| exact MV]. }
  walk_lia_to 0x88dd8.
  gen2 CONTB 0x88de0 17%nat 5%nat.
  { intros y17 y5.
    step. zstep. step. if_cases K1; zify_cond K1.
    -   step. if_cases K2; zify_cond K2.
      + replace (A + i + 1)%Z with (A + (i + 1))%Z by lia. apply CONT. lia.
      + zstep. step. replace (A + i + 2)%Z with (A + (i + 2))%Z by lia. apply CONT. lia.
    - step. if_cases K3; zify_cond K3.
      +
        walk_lia_to 0x88f70. chk8 11 (T + 8) SHWT.
        walk_lia_to 0x88f90. chk8 12 (T + 8) SHWT.
        walk_lia_to 0x88e84.
        replace (A + i + 1 - (A + cur))%Z with (i + 1 - cur)%Z in * by lia.
        apply (tailA (i + 1 - cur) 5); try lia. mv_tacA FR.
      + step. if_cases K4; zify_cond K4.
        *   zstep. step. if_cases K5; zify_cond K5.
          -- apply (ret_errA 3) with (tc1 := wz (A + cur)) (tc2 := tc2); [exact MV| right; reflexivity].
          -- zstep. zstep. step. if_cases K6; zify_cond K6.
             ++ replace (A + i + 1)%Z with (A + (i + 1))%Z by lia. apply CONT. lia.
             ++ step. apply (ret_errA 3) with (tc1 := wz (A + cur)) (tc2 := tc2); [exact MV| right; reflexivity].
        * step. if_cases K7; zify_cond K7.
          --   replace (A + i + 1)%Z with (A + (i + 1))%Z by lia. apply CONT. lia.
          --   zstep. step. if_cases K8; zify_cond K8.
             ++ apply (ret_errA 3) with (tc1 := wz (A + cur)) (tc2 := tc2); [exact MV| right; reflexivity].
             ++ exfalso. lia. }
  chkw 17 (A + i) 1 SHWA' kk SHR Hk.
  destruct Hk as [-> | [G1 G2]].
  - step. step. lit_branch. apply CONTB.
  - step. step. rewrite (sxb_small kk) by lia. if_cases G3; zify_cond G3; [| exfalso; lia].
    zstep. step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
    apply CONTB.
Qed.

#[using="HC LBS CUR AE0 SHWS SHWT SHWY SHWA SLO SHI MLO TLO THI TPAR TAA THI2 TAL YLO YHI YHI2 YAL ABHI MBS TTY APAR CLO LO"] Lemma ws_startA : forall x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x27 x28 x29 x30 x31 m,
  minvA m tw1 tw2 -> cur < len ->
  evt asegs POST (LSTA 0x88b10 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (A + cur)) x21 (Z_to_bv 64 (A + len)) (Z_to_bv 64 len)
                       x27 x28 x29 x30 x31 m).
Proof.
  intros until m. intros ([j24 FR] & ST & SC & MBC & BUF & TC & TYC & MI & MU & WM) HCL.
  pose proof alloc_ceiling_range as ACR; unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
  walk_lia_to 0x88b18. chk8 10 T SHWT.
  walk_lia_to 0x88b28. step. if_cases K1; zify_cond K1.
  - replace (A + cur + 1)%Z with (A + (cur + 1))%Z by lia. apply (ws_endA (cur + 1)) with (tc2 := tw2); [mv_tacA FR| lia].
  - walk_lia_to 0x88b54.
    replace (Z_to_bv 64 (Z.lxor cur 18446744073709551615 + len)) with (Z_to_bv 64 (len - (cur + 1)))%Z.
    2:{ apply Z_to_bv_eqm. rewrite zb_lxor_ones by lia. change 18446744073709551615%Z with (2^64 - 1)%Z.
        rewrite <- (Z.mod_add (len - (cur + 1)) 1 (2^64)) by lia. f_equal. lia. }
    replace (A + cur + 1)%Z with (A + (cur + 1))%Z by lia.
    apply (ws_loopA (Datatypes.S (Z.to_nat (len - cur))) (cur + 1)) with (tc2 := tw2); [lia| lia| mv_tacA FR].
Qed.

#[using="HC LBS CUR AE0 SHWS SHWT SHWY SLO SHI MLO TLO THI TPAR TAA THI2 TAL YLO YHI YHI2 YAL ABHI MBS TTY APAR CLO LO"] Lemma lf_blkA : forall (b0 : byte) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x25 x26 x27 x28 x29 x30 x31 m,
  minvA m tw1 tw2 -> cur < len -> nth_error bs (Z.to_nat cur) = Some b0 -> bv_unsigned b0 = 10 ->
  evt asegs POST (LSTA 0x88cd0 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (A + cur)) x21 x25 x26 x27 x28 x29 x30 x31 m).
Proof.
  intros until m. intros ([j24 FR] & ST & SC & MBC & BUF & TC & TYC & MI & MU & WM) HCL Hb0 Hc10.
  pose proof alloc_ceiling_range as ACR; unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
  walk_lia_to 0x88cd8. chk8 10 T SHWT.
  walk_lia_to 0x88cf0. chk8 11 (T + 8) SHWT.
  walk_lia_to 0x88d10. chk8 12 (T + 8) SHWT.
  walk_lia_to 0x88e84.
  apply (tailA 1 2); try lia. mv_tacA FR. intros _ i Hi; assert (i = cur) by lia; subst i; exists b0; split; [exact Hb0| lia].
Qed.

#[using="HC LBS CUR AE0 SHWS SHWT SHWY SHWA SLO SHI MLO TLO THI TPAR TAA THI2 TAL YLO YHI YHI2 YAL ABHI MBS TTY APAR CLO LO"] Lemma cr_blkA : forall (b0 : byte) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x26 x27 x28 x29 x30 x31 m,
  minvA m tw1 tw2 -> cur < len -> nth_error bs (Z.to_nat cur) = Some b0 -> bv_unsigned b0 = 13 ->
  evt asegs POST (LSTA 0x88d1c x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (A + cur)) x21 (Z_to_bv 64 (A + len)) x26 x27 x28 x29 x30 x31 m).
Proof.
  intros until m. intros ([j24 FR] & ST & SC & MBC & BUF & TC & TYC & MI & MU & WM) HCL Hb0 Hc13.
  pose proof alloc_ceiling_range as ACR; unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
  walk_lia_to 0x88d24. chk8 10 T SHWT.
  walk_lia_to 0x88d38. step. if_cases K1; zify_cond K1.
  - apply (ret_errA 1) with (tc1 := wz (A + cur)) (tc2 := tw2); [mv_tacA FR| left; reflexivity].
  - destruct (nth_bsA (cur + 1) ltac:(lia)) as [b1 Hb1]. pose proof (byte_rangeA b1) as BR1.
    pose proof (u8ro_read asegs _ A bs (cur + 1) b1 (Z_to_bv 64 (A + cur + 1)) BUF Hb1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD1.
    pose proof (SHWA ltac:(lia)) as SHWA'.
    walk_lia_to 0x88d44.
    gen2 CONT 0x88d4c 10%nat 12%nat.
    { intros y10 y12.
      step. zstep. zstep. step. if_cases K2; zify_cond K2.
      +
        walk_lia_to 0x88f0c. chk8 11 (T + 8) SHWT.
        walk_lia_to 0x88f58. chk8 12 (T + 8) SHWT.
        walk_lia_to 0x88e84.
        apply (tailA 1 3); try lia. mv_tacA FR.
      +
        walk_lia_to 0x88d64. chk8 11 (T + 8) SHWT.
        walk_lia_to 0x88d80. chk8 12 (T + 8) SHWT.
        walk_lia_to 0x88e84.
        apply (tailA 2 2); try lia. mv_tacA FR. intros _ i Hi. assert (HI : i = cur \/ i = cur + 1) by lia.
        destruct HI as [-> | ->]; [exists b0; split; [exact Hb0| lia]| exists b1; split; [exact Hb1| right; lia]]. }
    chkw 10 (A + cur + 1) 1 SHWA' kk SHR Hk.
    destruct Hk as [-> | [G1 G2]].
    + step. step. lit_branch. apply CONT.
    + step. step. rewrite (sxb_small kk) by lia. if_cases G3; zify_cond G3; [| exfalso; lia].
      zstep. step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
      apply CONT.
Qed.

#[using="HC LBS CUR AE0 SHWS SHWT SHWY SHWA SLO SHI MLO TLO THI TPAR TAA THI2 TAL YLO YHI YHI2 YAL ABHI MBS TTY APAR CLO LO"] Lemma quote_startA : forall x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x26 x27 x28 x29 x30 x31 m,
  minvA m tw1 tw2 -> cur < len ->
  evt asegs POST (LSTA 0x88d8c x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (A + cur)) x21 (Z_to_bv 64 (A + len)) x26 x27 x28 x29 x30 x31 m).
Proof.
  intros until m. intros ([j24 FR] & ST & SC & MBC & BUF & TC & TYC & MI & MU & WM) HCL.
  pose proof alloc_ceiling_range as ACR; unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
  walk_lia_to 0x88d94. chk8 10 T SHWT.
  walk_lia_to 0x88da4. step. if_cases K1; zify_cond K1.
  - zstep. step. apply (ret_errA 1) with (tc1 := wz (A + cur)) (tc2 := tw2); [mv_tacA FR| left; reflexivity].
  - walk_lia_to 0x88dd0.
    replace (A + cur + 1)%Z with (A + (cur + 1))%Z by lia.
    apply (quote_loopA (Datatypes.S (Z.to_nat (len - cur))) (cur + 1)) with (tc2 := tw2); [lia| lia| mv_tacA FR].
Qed.

#[using="HC IC LBS CUR AE0 SHWS SHWT SHWY SHWA SHWP SLO SHI MLO TLO THI TPAR TAA THI2 TAL YLO YHI YHI2 YAL ABHI MBS TTY APAR CLO QHI LO"] Lemma dispatchA : forall (c : Z) (b0 : byte) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 m,
  minvA m tw1 tw2 -> cur < len -> 0 <= c < 256 -> nth_error bs (Z.to_nat cur) = Some b0 -> c = bv_unsigned b0 ->
  evt asegs POST (LSTA 0x88ae8 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (A + cur)) (Z_to_bv 64 c) (Z_to_bv 64 (A + len)) (Z_to_bv 64 len)
                       x27 x28 x29 x30 x31 m).
Proof.
  intros until m. intros MV HCL Hc Hb0 Hcb. pose proof MV as ([j24 FR] & ST & SC & MBC & BUF & TC & TYC & MI & MU & WM).
  pose proof alloc_ceiling_range as ACR; unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
  zstep. zstep. step. if_cases KR; zify_cond KR.
  -   apply default_blkA; [exact MV| lia| lia].
  -
    assert (CR : 9 <= c <= 34).
    { destruct (Z.lt_ge_cases c 9); [|lia]. exfalso. revert KR.
      rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia. }
    pose proof (jt_read_A m c MI CR) as RD.
    zstep. zstep. zstep. zstep.
    replace (wa (JTAB_A + 4 * (c - 9))) with (Z_to_bv 64 (Z.shiftl (c + -9) 2 + 136024))%Z in RD
      by (unfold wa, JTAB_A; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    step. zstep.
    assert (CASES : (jt_off_A c = 423864 /\ (c = 9 \/ c = 32)) \/ (jt_off_A c = 424312 /\ c = 10) \/ (jt_off_A c = 424388 /\ c = 13)
                    \/ (jt_off_A c = 424500 /\ c = 34) \/ (jt_off_A c = 424212 /\ c <> 9 /\ c <> 32 /\ c <> 10 /\ c <> 13 /\ c <> 34)).
    { unfold jt_off_A. destruct (Z.eqb_spec c 9); [subst; cbn; lia|]. destruct (Z.eqb_spec c 32); [subst; cbn; lia|]. cbn [orb].
      destruct (Z.eqb_spec c 10); [lia|]. destruct (Z.eqb_spec c 13); [lia|]. destruct (Z.eqb_spec c 34); lia. }
    destruct CASES as [[E Hc9]|[[E Hc10]|[[E Hc13]|[[E Hc34]|[E Hoth]]]]]; rewrite E; rewrite sx32_lit by lia; rewrite ?unsigned_lit by lia; step.
    +   apply ws_startA; [exact MV| lia].
    +   apply (lf_blkA b0); [exact MV| lia| exact Hb0| lia].
    +   apply (cr_blkA b0); [exact MV| lia| exact Hb0| lia].
    +   apply quote_startA; [exact MV| lia].
    +   apply default_blkA; [exact MV| lia| lia].
Qed.

#[using="HC IC LBS CUR AE0 SHWS SHWM SHWT SHWY SHWA SHWP SLO SHI SAL MLO MAL TLO THI TPAR TAA THI2 TAL YLO YHI YHI2 YAL ABHI MBS TTY APAR CLO QHI LO"] Lemma bodyA : forall t0 t1 t2 x13 x14 x15 x16 x17 t3 t4 t5 t6,
  rw_cells asegs m0 S [C8 (wz MB); C8 (wz cur); C4 (wz 0)] ->
  rw_cells asegs m0 MB [C8 (wz A); C8 (wz len); C8 (wz cap); C8 (wz 5)] ->
  bytes_at asegs m0 A bs -> rw_cells asegs m0 T [C8 tw1; C8 tw2] -> rw_cells asegs m0 TY [C4 tyw] ->
  stk asegs m0 lo q -> mem_inv asegs m0 ->
  evt asegs POST
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 T) (Z_to_bv 64 TY) x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 sgt_entryA) fc None m0 (seg_rom asegs)).
Proof.
  intros until t6. intros SC MBC BUF TC TYC ST MI. unfold sgt_entryA.
  a0_prologue AE0 [(lo, q); (S + 8, S + 16); (T, T + 16); (TY, TY + 4)]%Z m0.
  pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
  carve_frame 128%nat ST.
  walk_lia_to 0x88a48. chk8 10 S SHWS.
  walk_lia_to 0x88a60. chk8 11 MB SHWM.
  walk_lia_to 0x88a74. chk8 23 (S + 8) SHWS.
  walk_lia_to 0x88a88. chk8 12 (MB + 8) SHWM.
  walk_lia_to 0x88a98. step. if_cases K0; zify_cond K0.
  2:{   zstep. step.
      apply (ret_errA 1) with (tc1 := tw1) (tc2 := tw2); [| left; reflexivity]. mv_tacA FR. }
  assert (HCL : cur < len) by lia.
  destruct (nth_bsA cur ltac:(lia)) as [b0 Hb0]. pose proof (byte_rangeA b0) as BR0.
  pose proof (u8ro_read asegs _ A bs cur b0 (Z_to_bv 64 (A + cur)) BUF Hb0 ltac:(lia) eq_refl) as RD0.
  pose proof (SHWA ltac:(lia)) as SHWA'.
  walk_lia_to 0x88ab4.
  gen2 CONT 0x88abc 10%nat 11%nat.
  { intros y10 y11.
    step. zstep. zstep. zstep. step. if_cases K1; zify_cond K1.
    - apply (dispatchA (bv_unsigned b0) b0); [mv_tacA FR| lia| lia| exact Hb0| reflexivity].
    - zstep. zstep. zstep. zstep. step.
      env_now AE0 MU WM.
      call_memchr (bv_unsigned b0).
      clear RD0 AE PC0 POST. rename MI0 into MI. rename PC into ST.
      pose proof (P0.H_scanner_get_token.memchr_res_small SEPTAB_A (bv_unsigned b0) 20 sep20 ltac:(unfold SEPTAB_A; lia)) as MR.
      cbn [length P0.H_scanner_get_token.sep20 map] in MR. unfold SEPTAB_A in MR.
      step. if_cases K2; zify_cond K2.
      + apply ident_startA; [mv_tacA FR| lia].
      + apply (dispatchA (bv_unsigned b0) b0); [mv_tacA FR| lia| lia| exact Hb0| reflexivity]. }
  chkw 10 (A + cur) 1 SHWA' kk SHR Hk.
  destruct Hk as [-> | [G1 G2]].
  - step. step. lit_branch. apply CONT.
  - step. step. rewrite (sxb_small kk) by lia. if_cases G3; zify_cond G3; [| exfalso; lia].
    zstep. step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
    apply CONT.
Qed.

End W.

Theorem scanner_get_token_spec_A {HC : HasCeiling} (IC : icpt_contracts) : sgt_stmt_A.
Proof.
  unfold sgt_stmt_A. intros until m.
  intros SC MBC BUF LBS CUR CAP AHI TC TYC AE0 SHWS SHWM SHWT SHWY SHWA SHWP SLO SHI SAL MLO MHI MAL TLO THI TAL YLO YHI YAL ALO ABHI MBS TTY TPAR TAA APAR ST CLO QHI LO MI -> -> ->.
  unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in MBC.
  assert (LO' : lo <= q + -128 - 4096) by (unfold A0_RT_STACK in LO; lia).
  assert (THI2 : T + 16 <= 2^47) by (pose proof (shw_win_ok _ _ _ SHWT) as WK; unfold win_ok in WK; lia).
  assert (YHI2 : TY + 4 <= 2^47) by (pose proof (shw_win_ok _ _ _ SHWY) as WK; unfold win_ok in WK; lia).
  eapply (bodyA IC S T TY MB A cur len cap lo q bs tw1 tw2 tyw); eauto.
Qed.
